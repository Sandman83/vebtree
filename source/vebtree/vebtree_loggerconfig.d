module vebtree_loggerconfig; 
import std.experimental.logger; 
enum logLevel = LogLevel.all; 

/+
enum LogLevel : ubyte
{
    all = 1, /** Lowest possible assignable $(D LogLevel). */
    trace = 32, /** $(D LogLevel) for tracing the execution of the program. */
    info = 64, /** This level is used to display information about the
                program. */
    warning = 96, /** warnings about the program should be displayed with this
                   level. */
    error = 128, /** Information about errors should be logged with this
                   level.*/
    critical = 160, /** Messages that inform about critical errors should be
                    logged with this level. */
    fatal = 192,   /** Log messages that describe fatal errors should use this
                  level. */
    off = ubyte.max /** Highest possible $(D LogLevel). */
}
+/